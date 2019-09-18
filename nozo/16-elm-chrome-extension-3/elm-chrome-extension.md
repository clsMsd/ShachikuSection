# Elmでchrome拡張をつくる備忘録 その３

今回はElmとJSの通信方法であるPortを使ってみる。

```elm
port module Background exposing (..)

main = Platform.worker { init = init
                       , update = update
                       , subscriptions = subscriptions
                       }

type alias Model = {}
type alias Msg = {}

port notify : () -> Cmd msg

init : () -> (Model, Cmd Msg)
init _ = Debug.log "Background is inited!" ({}, notify ())

update : Msg -> Model -> (Model, Cmd Msg)
update msg model = ({}, Cmd.none)

subscriptions : Model -> Sub Msg
subscriptions model = Sub.none
```

```js
var app = Elm.Background.init();

app.ports.notify.subscribe(function() {
    chrome.notifications.create(options = {
        type : "basic",
        iconUrl : "./img/sample.png",
        title : "Sample Title",
        message : "Sample message"
    });
});
```