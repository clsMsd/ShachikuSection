# 文字列をtoStringしたらコードの挙動が変わった話

## 始めに


### DefinePlugin
DefinePluginとはWebpackに付属しているプラグインの1つで、ビルド時にコード中の定数を置き換えることができる。
例えば、こんな感じでWebpackの設定を書いたとする。

```javascript
const path = require('path');
const { DefinePlugin } = require('webpack');
const dist = path.resolve(__dirname, 'dist');

module.exports = {
  mode: 'production',
  entry: "./main.js",
  output: {
    path: dist
  },
  plugins: [
    new DefinePlugin({
      hoge: JSON.stringify("a")
    })
  ],
}
```

すると、以下のコードで1が出力されるようになる。
```javascript
console.log(hoge) // => a
```

DefinePluginの挙動で注意するべき点は、変数が指定のリテラルに置き換えられるということである。  
例えば、上のコードのビルド結果は下のようになる。
```javascript
console.log("a")
```

## 起こったこと

問題のプロジェクトでは package.json に次の様に書いてあり、
```
  ...
  "build-stg": "NODE_ENV='staging' webpack",
  ...
```

webpack.config.js が次のようになっていた。
```javascript
const webpack = require('webpack');

module.exports = {
  mode: "production",
  entry: './main.js',
  plugins: [
    new webpack.DefinePlugin({
      "process": {
        env: JSON.stringify({ NODE_ENV: process.env.NODE_ENV })
      }
    })
  ]
};
```

ビルドするjsファイルの内容が次のようなものだった。  
```javascript
console.log(process.env.NODE_ENV)
```

このコードを実行すると、コンソールには `production` と出力される。  
これだけで「は？」という感じだが、更に恐ろしいのは次の挙動である。

```javascript
console.log(JSON.stringify(process.env))
```

このコードを実行するとなんと `{"NODE_ENV":"staging"}` と表示されるのである(！)

```javascript
console.log(process.env.NODE_ENV)               // => production
console.log(process.env["NODE_ENV"])            // => production
console.log(process.env["NODE_ENV".toString()]) // => staging
```

## 種明かし
実は`NODE_ENV`という変数はWebpackで特別扱いされており、webpackの`mode`の設定値で上書きされる挙動になっている。  
今回はproductionモードでビルドしているので、`NODE_ENV`が`production`で上書きされていたのである。  

一方definePluginは単純な文字列レベルの置換に近い処理しかしないため、
`process.env.NODE_ENV`と`process.env["NODE_ENV"]`は`production`に置き換えられたが、
`process.env["NODE_ENV".toString()]`は`process.env`が指定値で置き換えられて、`staging`と表示されたのである。

## どうするべきだった？

そもそも NODE_ENV に development と production 以外の値を入れるべきではない。

環境毎にAPIの向き先などを変更したいなら、`APP_ENV`とか`TARGET_ENV`などの変数を別途定義するべきである。  

例えば、dev環境を社内向け検証環境、stg環境を顧客向け検証環境、prod環境を本番環境として運用しているプロジェクトがあったとする。
ここで単純に「dev環境向けビルドはdevelopmentモードで行う」ということを前提にするとどうなるだろうか？

1. 社内テストではdevelopmentビルドのため顕在化しなかった不具合が顧客環境で発覚する
1. 顧客向け検証環境で問題が発生しても調査ができない

そもそも本番環境と開発環境で設定を変えるのはだいたい次のような理由が大きいだろう
1. サーバーや各種APIの向き先、設定値が異なる
1. ログ出力やデバッグ用シンボルの出力のOn/Offを切り替えたい
1. 最適化の有無を切り替えたい

実際に要求されるこれらの条件の組み合わせはプロジェクトによって異なるし、開発の進行具合によっても変わってくる。
なのでこれらの設定はひとまとめにせず、次のように個別に設定できるようにするべきであった。

サーバーや各種APIの向き先、設定値: `TARGET_ENV` などの、デプロイ先環境に基づく値
ログ出力の有無: 専用のloggerを用意して切り替え(logger自体の設定の切り替えをどうするかは課題であるが、他の設定値と強結合しないようにする)
最適化の有無: ビルドツールにそれ用の設定があると思うので、それに任せる
