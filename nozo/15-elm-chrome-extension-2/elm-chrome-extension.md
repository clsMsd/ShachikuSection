# Elmでchrome拡張をつくる備忘録 その２

今回はchrome拡張の構成とそれをElmで生成する方法を調査する。

## chrome拡張の基本構成

chrome拡張は以下のスクリプト・HTMLで構成される。

- Background Script
  - ブラウザ全体で発生したイベントを処理するスクリプト。例えば、ページの移動、ブックマークの削除、タブを閉じるなどのイベントを検出することができる。
- UI Elements
  - 拡張のUI。拡張のアイコンをクリックすると表示されるポップアップがこれにあたる。その他にも右クリックメニュー、キーボードショートカット、omniboxなどを定義する。
- Content Script
  - ブラウザに表示されたページの内容にアクセスできるスクリプト。ページのDOM情報を取得したり、書き換えたりすることができる。
  - **アクセスできるchrome APIに制限がある。** (詳細:https://developer.chrome.com/extensions/content_scripts)
- Options Page
  - 拡張の設定画面。

また、以下のように各スクリプトは互いにメッセージを送受信することが可能である。

![](./img/messagingarc.png)

引用：https://developer.chrome.com/extensions/overview


また、chrome拡張はmanifest.jsonファイルで読み込むスクリプトや権限の設定を行う。
例えば、Background Scriptのみで構成されるchrome拡張は以下のように定義される。

```shell
$ ls
background1.js  background2.js  manifest.json
$ cat manifest.json
{
    "name" : "Elm extension",
    "version" : "1.0",
    "description" : "generate extension from Elm",
    "manifest_version" : 2,
    "background" : {
        "scripts" : ["background1.js", "background2.js"],
        "persistent" : false
    }
}
```

## Elmからスクリプトを生成する方法

Background ScriptやContent ScriptはJSファイル単体で動作する。
このようなUIが存在しないプログラムをElmで生成する場合、以下の関数をエントリポイントとして用いる。

```elm
worker :
    { init : flags -> ( model, Cmd msg )
    , update : msg -> model -> ( model, Cmd msg )
    , subscriptions : model -> Sub msg
    }
    -> Program flags model msg
```

https://package.elm-lang.org/packages/elm/core/latest/Platform

`worker`を用いた何もしないプログラムは以下のように書ける。

```elm
main = Platform.worker { init = init
                       , update = update
                       , subscriptions = subscriptions
                       }

type alias Model = {}
type alias Msg = {}

init : () -> (Model, Cmd Msg)
init _ = Debug.log "Print message from Elm!" ({}, Cmd.none)

update : Msg -> Model -> (Model, Cmd Msg)
update msg model = ({}, Cmd.none)

subscriptions : Model -> Sub Msg
subscriptions model = Sub.none
```

このElmプログラムを以下のようにJSへコンパイルすることができる。

```shell
$ elm make src/Main.elm --output=main.js
```

コンパイルしたJSをmanifest.jsonでロードするように設定して、読み込み側のJSから`Elm.Main.init()`を実行することでElmプログラムを初期化することができる。

```shell
$ cat manifest.json 
{
    "name" : "Elm extension",
    "version" : "1.0",
    "description" : "generate extension from Elm",
    "manifest_version" : 2,
    "background" : {
        "scripts" : ["main.js", "background.js"],
        "persistent" : false
    }
}
$ cat background.js 
// Initialize extension
chrome.runtime.onInstalled.addListener(function() {
    console.log("Initializing extension...");

    // Initialize Elm program
    var app = Elm.Main.init();
});
```

このchrome拡張をインストールすると以下のようなログが出力される。

```
> Initializing extension...
> Print message from Elm!: ({},<internals>)
```

# 参考文献
- Develop Extensions - Chrome: developer - Google Chrome, https://developer.chrome.com/extensions/devguide
- 公式ドキュメント(翻訳ver)：https://guide.elm-lang.jp/
