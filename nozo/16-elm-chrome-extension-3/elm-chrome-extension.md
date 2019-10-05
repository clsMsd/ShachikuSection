# Elmでchrome拡張をつくる備忘録 その３

今回はElmとJSの通信方法であるPortを使ってみる。

## コマンドとサブスクリプション

Elmは外部で定義されたJSの関数を直接呼出したり、JSのデータを編集したりすることはできない。
そのため、外部とのやり取りはコマンドとサブスクリプションという仕組みを用いる。

![](https://guide.elm-lang.jp/effects/diagrams/element.svg)

引用：https://guide.elm-lang.jp/effects/

上図のように、これまでは表示したい内容を`Html`として渡していたのに加えて`Cmd`と`Sub`をランタイムシステムに渡す。

- `Cmd`はhttpリクエストや外部で定義したJS関数の実行をランタイムシステムに依頼することができる。
- `Sub`はタイマーなどのイベントに対するイベントリスナーをランタイムシステムに登録することができる。

`Cmd`と`Sub`は以下のようにinit, update, subscriptionsからランタイムシステムに渡す。

```elm
worker
  : { init : flags -> ( model, Cmd msg )
    , update : msg -> model -> ( model, Cmd msg )
    , subscriptions : model -> Sub msg
    }
  -> Program flags model msg
```

## Portを使ったJSとの通信

`Cmd`の例として、ElmからJSへ値を渡してランタイム側で処理するElmプログラムを以下に示す。

```elm
port module Background exposing (..)

port notify : String -> Cmd msg

main = Platform.worker { init = init
                       , update = update
                       , subscriptions = subscriptions
                       }

type alias Model = {}
type alias Msg = {}

init : () -> (Model, Cmd Msg)
init _ = ({}, notify "Sample message")

update : Msg -> Model -> (Model, Cmd Msg)
update msg model = ({}, Cmd.none)

subscriptions : Model -> Sub Msg
subscriptions model = Sub.none
```

ElmとJSのやりとりはPortと呼ばれる仕組みを用いる。

`port`をつけて宣言した関数は型の定義のみで、その実装をElm側では持たない。
この例では`String`を引数として受け取り、`Cmd msg`型の値を返す関数として宣言している。

```elm
port notify : String -> Cmd msg
```

以下のように`String`の値を渡すことで、JS側に値を渡すことができる。

```elm
init : () -> (Model, Cmd Msg)
init _ = ({}, notify "Sample message")
```

この値を受け取るJS側の実装は以下のように書ける。
`app.ports.notify.subscribe`に渡した関数がElm側で`notify`を呼び出したときに実行される。

```js
var app = Elm.Background.init();

app.ports.notify.subscribe(function(message) {
    chrome.notifications.create(options = {
        type : "basic",
        iconUrl : "./img/sample.png",
        title : "Sample Title",
        message : message
    });
});
```

続いて、`Sub`の例としてJSから値を受け取るElmプログラムを以下に示す。

```elm
port module Content exposing (..)

port observe : (String -> msg) -> Sub msg

main = Platform.worker { init = init
                       , update = update
                       , subscriptions = subscriptions
                       }

type alias Model = {}
type Msg = Changed String

init : () -> (Model, Cmd Msg)
init _ = ({}, Cmd.none)

update : Msg -> Model -> (Model, Cmd Msg)
update msg model =
    case msg of
        Changed text -> Debug.log ("Received Changed message : " ++ text) ({}, Cmd.none)

subscriptions : Model -> Sub Msg
subscriptions model =
    observe Changed
```

Elmが外部から値を`Msg`によって受け取る。
`Sub`として宣言する関数の第1引数には、ランタイム側から送られてくる`Msg`の種類を渡す。

```elm
port observe : (String -> msg) -> Sub msg
```

この例では、`Sub`として登録したイベントリスナーは、イベントが発生したときElmに対して`Changed`という`Msg`型の値を渡すことを示す。

```elm
type Msg = Changed String

subscriptions : Model -> Sub Msg
subscriptions model =
    observe Changed
```

`Msg`の処理はこれまで通りで、`Msg`の値をパターンマッチして処理する。

```elm
update : Msg -> Model -> (Model, Cmd Msg)
update msg model =
    case msg of
        Changed text -> Debug.log ("Received Changed message : " ++ text) ({}, Cmd.none)
```

portに対応するJS側の実装は以下のように書ける。
`app.ports.observe.send`関数を実行することで、Elm側に`Msg`型の値が渡される。

```js
var app = Elm.Content.init();

const obs = new MutationObserver((recs) => {
    recs.forEach((rec) => {
        rec.addedNodes.forEach((node) => {
            app.ports.observe.send(node.nodeName);
        });
    });
});

obs.observe(document, {childList:true, subtree:true, attributes:false, characterData:false});
```
