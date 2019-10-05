# C/C++の未定義動作とその恐怖

## はじめに
C++は高速化のために安全性を犠牲にしているとよく言われるが、  
最近のコンパイラはプログラム中の未定義動作を最適化のために積極的に活用するという恐ろしいことをしている。  
実際にC++で未定義動作を含むコードを書くとどのようなことが起こるのか、紹介する。  

## 未定義動作とは
C++の規格上、未定義動作と紛らわしい用語として「処理系定義の動作」「未規定動作」という用語があるので解説する。  

- 処理系定義の動作(implementation-defined behavior):  
    処理系は考えられる動作のうちの1つを一貫して行う。処理系はドキュメントにその動作を定義する必要がある。  
    例: sizeof(int) の値
        int型のサイズは処理系によって変わるが、同じ処理系ならば必ず同じである必要がある。  
- 未規定動作(unspecified behavior):  
    処理系は考えられる動作の内の1つを行う。その動作は一貫してなくてもよい。  
    例: f() + g() や h(f(), g()) と書いたときの式の評価順序  
        プログラム中のある行では f() が先に評価され、別の行では g() が先に評価されるということが許される。  
- 未定義動作(undefined behavior):  
    処理系が実際に行う動作について標準規格が<b>如何なる要件もおかない</b>。  
    例: いろいろ  

## いろいろな未定義動作
実際にC/C++の未定義動作と、他の言語(C#)での同じ動作の扱いについて見てみよう。  

### 未初期化のローカル変数の使用
```c
int main() {
    int a;
    printf("%d\n", a);
    return 0;
}
```
ちなみにC/C++でもグローバル変数やstatic変数は自動的に初期化されるので使用しても未定義動作にはならない。  

C# では未初期化の値型の変数は0, 参照型はNullであると決まっている。  

### 符号付き整数のオーバーフロー
```c
#include <limits.h>   

int main() {
    int a = INT_MAX;
    printf("%d\n", a + 1);
    return 0;
}
```

C# ではcheckedとuncheckedの2つのモードがあり、オーバーフローをチェックするかどうかを明示的に選択することができる(デフォルトではunchecked)。
checked, uncheckedの指定はコンパイルオプションで指定できる他、プログラム中で指定することもできる。  

### Nullポインタのデリファレンス
```c
int main() {
    int *a = NULL
    printf("%d\n", *a);
    return 0;
}
```

C# では `System.NullReferenceException` が発生する。  

### 配列の境界外参照
```c
int main() {
    int arr[3] = { 1, 2, 3 };
    printf("%d\n", arr[3]);
    return 0;
}
```

C# では `System.IndexOutOfRangeException` が発生する。  

### ゼロ除算
```c
int main() {
    printf("%d\n", 1/0);
    return 0;
}
```
C# では `System.DivideByZeroException` が発生する。  

### 副作用を起こさない無限ループ
```c
int main() {
    while(1) {}

    return 0;
}
```
C# では特に何もない。

### constな変数の書き換え
```c
int main() {
    const int a = 1;
    int *p = &a;

    *p = 2;

    return 0;
}
```

C# では `const` はコンパイル時定数なので書き換え不可(コンパイルエラー)。  
<br/>

このように C# の場合では例外が発生する動作が、C/C++の場合では未定義動作となっていることが非常に多い。  
C# でこれらの動作を起こした場合に決まった例外を発生させるということは、裏を返せば処理系がこれらの動作が起こらないか  
プログラムの実行中常に監視しているということであり、その分実行時のオーバーヘッドが発生する  
(実際にはオーバーヘッドを少なくするために、CPUからのトラップを使うこともある)。  
C/C++は Trust the programmer の精神で作られているので、そのような動作をするプログラムを書いてマズいことが起きたら  
それはプログラマの責任であるとして、安全性よりも実行速度を重視している。   

## 未定義動作を利用した現代的なコンパイラの最適化とその危険性
(この章のほぼ全ての内容は
https://cpplover.blogspot.com/2014/06/old-new-thing.html
(さらにその元ネタは https://devblogs.microsoft.com/oldnewthing/20140627-00/?p=633)
の丸パクリです)

C/C++の規格上では未定義動作が起きた際には処理系はいかなる動作を引き起こしてもよいとされている  
(このことから、C++プログラマは冗談で未定義動作を起こすと「鼻から悪魔が飛び出る」と言ったりする http://catb.org/jargon/html/N/nasal-demons.html)。  
このことから、現代的なコンパイラはコンパイル時にあるコードが必ず未定義動作を引き起こすということが分かっているときに、  
そのコードには到達不能であるという仮定のもと最適化を行うことがある。  
何故かというと、もしも仮定が正しくて実際の実行時にそのコードに到達しないならばそのような仮定をおいて問題ないし、  
もし仮定が間違っていて実行時にそのコードに到達した場合は未定義動作を起こすので「実際にはそのコードに到達しなかった」かのように動作しても問題ない  
(未定義動作が起きたときは「いかなる動作」を引き起こしてもよいので、当然「実際にはそのコードに到達しなかった」かのような動作を引き起こすことも許される)からである。

このコンパイラの最適化は一見すると不可解に思えるバグを生じさせることがある。  
  
例えば、次のように配列にある値が存在するかを判定する関数があったとする。  
```cpp
int array[4] = { 1, 2, 3, 4 };

bool exists_in_array(int value) {
    for (auto i = 0; i <= 4; i++) { // ありがちなforループのミス
        if (array[i] == value) return true;
    }

    return false;
}
```

このプログラムは `i = 4`のときに配列の境界外参照で未定義動作を起こす。  
未定義動作が生じた場合、処理系はどのような動作をしてもよいので、コンパイラは上のコードを次のように書き換えることができる。  

```cpp
int array[4] = { 1, 2, 3, 4 };

bool exists_in_array(int value) {
    for (auto i = 0; i <= 4; i++) { // ありがちなforループのミス
        if (array[i] == value) return true;
    }

    return true; // ここに到達したときは必ず未定義動作が生じているので、何をやってもよい
}
```

この関数は全てのコードパスで `true` を返すので、コンパイラはさらに次のようにコードを書き換えることができる。  
```cpp
int array[4] = { 1, 2, 3, 4 };

bool exists_in_array(int value) {
    return true;
}
```

実際に確かめてみると GCC8.3 では確かにこのように最適化される(https://ideone.com/0Au55f)。  

これだけでもかなりヤバいのだが、

次のように、ポインタがNullかどうかを調べて、Nullでない場合は参照先の値を、Nullの場合にはデフォルト値を返す関数があったとする。  
```cpp
int value_or_fallback(int *p) {
    return p ? *p : 42;
}
```

デバッグのためにこの関数に次のような変更を加えたとする。
```cpp
int value_or_fallback(int *p) {
    printf("The value of *p is %d\n", *p);
    return p ? *p : 42;
}
```

変更後のコードでは、ポインタがNullかどうかをチェックする前にデリファレンスしてしまっている。  
この結果、コンパイラは最適化の結果次のようにコードを変換するかもしれない。  
```cpp
int value_or_fallback(int *p) {
    printf("The value of *p is %d\n", *p);
    return *p;
}
```

この `value_or_fallback`関数が次のような関数で使われていたとする。  
```cpp
void unwitting(bool door_is_open) {
    if (door_is_open) {
        walk_on_in();
    } else {
        ring_bell();

        // wait for the door to open using the fallback value
        fallback = value_or_fallback(nullptr);
        wait_for_door_to_open(fallback);
    }
}
```

このコードは `else` 節で必ず未定義動作を起こすので、`else`節は決して実行されないと仮定することができる。  
この結果、非古典的なコンパイラは最適化の結果次のようにコードを変換するかもしれない。  
```cpp
void unwitting(bool door_is_open) {
    walk_on_in();
}
```

さらに `unwitting`関数が次のように使われていたとする。
```cpp
void keep_checking_door() {
    for (;;) {
        printf("Is the door open? ");
        fflush(stdout);
        char response;
        if (scanf("%c", &response) != 1) return;
        bool door_is_open = response == 'Y';
        unwitting(door_is_open);
    }
}
```

コンパイラは、`door_is_open` が `false` ならば未定義動作となることから、コードを次のように書き換えるかもしれない。  
```cpp
void keep_checking_door() {
    for (;;) {
        printf("Is the door open? ");
        fflush(stdout);
        char response;
        if (scanf("%c", &response) != 1) return;
        bool door_is_open = response == 'Y';
        if (!door_is_open) abort();
        walk_on_in();
    }
}
```

書き換え前のコードでは、プログラムはクラッシュする前に `ring_bell()` を実行するが、  
書き換え後のコードではプログラムは `ring_bell()` を実行する前にクラッシュする。  

これは、処理系は未定義動作が起きたときに過去に戻ってベルを鳴らさないようにしたと解釈することもできる。  
標準規格では未定義動作が生じた場合に「未定義動作に先行する操作も含めて、いかなる実行上の制約をも課すことはない」
としている。  
これは ファイルへの書き込みのような外部への操作も含まれる。  

## 参考資料
https://qiita.com/akinomyoga/items/592e5a3b8438a0c8556b  
https://rsk0315.hatenablog.com/entry/2019/09/10/213859  
https://cpplover.blogspot.com/2014/06/old-new-thing.html  
https://qiita.com/suzuki-kei/items/3782e0bdf89076cb4105
https://qiita.com/tkmtSo/items/de3148dd1dcb70f38d6a
https://ja.cppreference.com/w/cpp/language/ub
