# Deno

## はじめに
> Deno is a simple, modern and secure runtime for JavaScript and TypeScript that uses V8 and is built in Rust.  
>   
> Features  
> - Secure by default. No file, network, or environment access, unless explicitly enabled.  
> - Supports TypeScript out of the box.  
> - Ships only a single executable file.  
> - Built-in utilities like a dependency inspector (deno info) and a code formatter (deno fmt).  
> - Set of reviewed standard modules that are guaranteed to work with Deno.  
[https://github.com/denoland/deno より引用]

## Node.jsとの違い

### 1. Rustによる実装  
Node.jsとDenoのどちらもJavaScriptの実行エンジンとしてV8を使っているのは同じだが，Denoではそれ以外の部分はRustにより実装されており，
開発者が自分の足を撃ち抜きにくいようになっている。

### 2. TypeScriptのネイティブサポート
node.jsでTypeScriptを使用するにはtscでJavaScriptにトランスパイルするかts-nodeを使うなどする必要があるが，  
denoではTypeScriptがネイティブサポートされているのでそのまま実行できる。  

### 3. Promiseに対応した標準ライブラリ
node.jsの標準ライブラリはコールバック関数を使うことが多いが，  
Denoでは標準ライブラリもプロミスを返すようになっている。  

### 4. 簡潔なモジュールシステム  
例えば，node.jsで`require("foo")`というコードを実行した場合，
1. Node.jsの標準ライブラリの`foo`
1. `npm install`で追加した(`node_modules`配下の)`foo`パッケージ
1. `NODE_PATH`内(`NODE_PATH`が空の場合は`/usr/lib/node_modules`以下など)の`foo.js`
1. `NODE_PATH`内(`NODE_PATH`が空の場合は`/usr/lib/node_modules`以下など)の`foo/index.js`
あたりを探索する。  
さらにv8以降のNode.jsではES Module形式の`import`にも対応しており，拡張子や`package.json`の設定によって挙動を変えるなど更にカオスになっている。  
一方denoではCommonJS形式の`require`を使ったモジュールの読み込みはサポートされず，ES Module形式のモジュールの読み込みのみがサポートされる。  
さらにimport先の指定は絶対パス又は実行ファイルからの相対パスしか使えないので，読み込むモジュールが曖昧になることはない。  
またnpmのようなパッケージマネージャも必要ない。  

### 5. ブラウザとの互換性
Node.jsはJavaScript実行環境でありながら，ブラウザとは異なるJavaScriptの書き方を必要とすることが多かった。  
例えば上で述べたモジュールシステムがそうであるし，ブラウザにあるFetchAPIなどもNode.jsには実装されていない。  
一方denoではできるだけブラウザとの互換性のあるJavaScriptの書き方ができるようになっており，  
ファイルアクセスなどブラウザと非互換のAPIはDeno名前空間の下に配置するなど整理されたAPIになっている。  

### 6. デフォルトでセキュアなサンドボックス志向  
もともとはサーバーサイドJavaScript実行環境として開発されたnode.jsだったが，今日ではbabel/webpack/eslintなどの  
Webフロントエンド向け開発ツール類の実行環境としてもよく使われ，もはや汎用的なスクリプティングツールとなっている。  
その一方で，Node.js向けのパッケージにマルウェアを仕込むという攻撃が行われるようになってきている。  

Denoでは，起動時のフラグで明示的な権限を与えないとファイルやネットワークのアクセスが制限されるので，このような攻撃を緩和することができる。  

例えばNode.jsの場合よく分からないwebpackのプラグインを入れていたら勝手に暗号通貨の採掘を始めてネットワーク経由でどこかのサーバーに送金する，というようなことが考えられるが，
そもそも論としてモジュールバンドラにネットワークへのアクセス権は要らないのでDenoの場合はこのようなツールにはネットワークのアクセス権を与えないことで攻撃を無力化することができる。

(ただ個人的にはPythonやRubyのような他のスクリプト言語の処理系でもこのような機能はサポートしていないので，
この機能の必要性は若干疑問に感じる)

### 7. ネイティブエクステンション
Node.jsでネイティブコードを呼び出す場合はネイティブ拡張を作ることが多いらしいが，  
Node.jsのネイティブ拡張のビルドには node-gyp というビルドツールが必要になる。  
gyp というのはもともとV8のビルドに使われていたのでNode.jsでもこれを使っているらしいのだが，肝心のV8は今では別のビルドツールを使っており，  
gyp 自体実行にPython2.7 だったりとちょっとアレである。  

## 環境構築

bash
```
$ curl -fsSL https://deno.land/x/install/install.sh | sh
```

powershell
```
$ iwr https://deno.land/x/install/install.ps1 -useb | iex
```

rustを使っていてcargoをインストールしている場合はcargo経由でもインストールできる
```
$ cargo install deno
```

## サンプル

### Hello World
```ts
console.log("Hello World")
```
`deno run helloworld.ts` で実行。  
node.jsと同じ

### ファイルIO
```ts
const text = await Deno.readTextFile("./sample.txt");
await Deno.writeTextFile("./tmp.txt", text);
```

`deno run --allow-read --allow-write fileio.ts` で実行。  

ブラウザと非互換の標準APIは`Deno`名前空間の下にまとめられている。  
node.jsと異なりファイルIOに`Promise`を使っている。  

Node.js での実装
```js
const fs = require("fs")

fs.readFile("./sample.txt", "utf8", (err, text) => {
   fs.writeFile("./tmp.txt", text, () => {})
})
```

(実はNode.jsもファイルIOはプロミス版が用意されている)
```js
const fs = require("fs").promises
async function main() {
   const text = await fs.readFile("./sample.txt", "utf8")
   await fs.writeFile("./tmp.txt", text)
}

main();
```

### HTTPサーバー (標準ライブラリ)
```ts
import { serve } from "https://deno.land/std@0.71.0/http/server.ts";

const port = 3000
const app = serve({ port })

console.log(`Server started at port=${port}`)

for await (const req of app) {
   req.respond({ body: "Hello World" })
}
```

`deno run --allow-net serv.ts` で実行。

標準ライブラリであってもURLを直接指定して`import`する。  
キャッシュは透過的に扱われ(キャッシュが無ければ取りに行く。キャッシュがあればそれを見る)，  
プログラマがキャッシュについて意識する必要は無い(ということになっている)。  
(しかしこれ，ライブラリをホストしているサーバのURLが変わったらどうするのだろうか…)

### HTTPサーバー (Servest)
日本人が作っているServestというサーバーもあるので紹介する。
```ts
import { createApp } from "https://servestjs.org/@v1.1.5/mod.ts";
 
const app = createApp();

app.handle("/", async (req) => {
   await req.respond({
     status: 200,
     headers: new Headers({
       "content-type": "text/plain",
     }),
     body: "hello deno!",
   });
});

const port = 3000
app.listen({ port });
console.log(`Server started at port=${port}`)
```

### JSX
tscにはJSXのサポートも入っているので，テンプレートエンジンとしてJSXが使える。  
(拡張子は`.ts`ではなく`.tsx`にする)

```ts
import React from "https://dev.jspm.io/react/index.js";
import ReactDOMServer from "https://dev.jspm.io/react-dom/server.js";
import { createApp } from "https://servestjs.org/@v1.1.6/mod.ts";

const app = createApp();
app.handle("/", async (req) => {
  await req.respond({
    status: 200,
    headers: new Headers({
      "content-type": "text/html; charset=UTF-8",
    }),
    body: ReactDOMServer.renderToString(
      <html>
        <head>
          <meta charSet="utf-8" />
          <title>servest</title>
        </head>
        <body>Hello Servest!</body>
      </html>,
    ),
  });
});
app.listen({ port: 8899 });
```

## 参考資料
Node.js における設計ミス By Ryan Dahl [https://yosuke-furukawa.hatenablog.com/entry/2018/06/07/080335]
DenoとNode.jsの大きな違い [https://scrapbox.io/keroxp/Deno%E3%81%A8Node.js%E3%81%AE%E5%A4%A7%E3%81%8D%E3%81%AA%E9%81%95%E3%81%84]
