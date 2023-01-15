# WebAssembly not for Web

## WebAssembly とは？

> WebAssembly は現代のウェブブラウザーで実行できる新しい種類のコードです。ネイティブに近いパフォーマンスで動作する、コンパクトなバイナリー形式の低レベルなアセンブリー風言語です。さらに、 C/C++、C# や Rust などの言語のコンパイル先となり、それらの言語をウェブ上で実行することができます。 WebAssembly は JavaScript と並行して動作するように設計されているため、両方を連携させることができます。 (https://developer.mozilla.org/ja/docs/WebAssembly より引用)

### WebAssembly の特徴

- OSやCPUに依存しない中間表現の実行形式である
- 安全性に配慮した設計がされている
- Bytecode Allianceという非営利団体が規格の策定をしている

## 処理系のインストール

- wasmtime
- wasmer
- node.js, deno, chrome 等

### wasmtime
```bash
$ curl https://wasmtime.dev/install.sh -sSf | bash
```
インストール完了後、新しいターミナルを開くと`wasmtime`コマンドが使えるようになる

### wasmer
```bash
$ curl https://get.wasmer.io -sSfL | sh -s "v3.1.0" 
```

インストール完了後、新しいターミナルを開くと`wasmer`コマンドが使えるようになる

### wabt(アセンブラ・逆アセンブラ)
wabt (https://github.com/WebAssembly/wabt)
```bash
$ npm i -g wabt
```

インストール完了後、`wat2wasm` `wasm2wat` コマンドが使えるようになる。

### Hello World (Rust)
Rustはインストール後そのままの状態ではビルドターゲットにwasmが入っていないので、以下のコマンドでビルドターゲットにwasmを追加する。

```bash
$ rustup target add wasm32-wasi
```

```rust
fn main() {
  println!("Hello Wasm");
}
```

ビルド・実行
```bash
$ rustc hello_world.rs --target=wasm32-wasi
$ wasmtime hello_world.rs
```

### Hello World (C言語)
clang のビルドターゲットには wasm が含まれているのでなんかちゃんとすればビルドできるらしいのだが、今回はwasi-sdkというものを使う。
https://github.com/WebAssembly/wasi-sdk/releases から自分の環境向けのassetをダウンロードして適当なディレクトリに展開すれば良い。

```c
#include <stdio.h>

int main() {
  printf("Hello Wasm\n");

  return 0;
}
```

ビルド・実行
```bash
$ ~/tools/wasi-sdk-17.0/bin/clang hello.c
$ wasmtime a.out
```
