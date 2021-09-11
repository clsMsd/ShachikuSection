# WebSocketの紹介

## WebSocketとは？
Http通信ではクライアントからのリクエストに対してサーバーがレスポンスするという動作が基本になっているが、  
これではサーバーから能動的にクライアントに通知を送るようなことができない。  
これは例えばリアルタイムなチャットアプリなどを作ろうとした場合に問題になることが分かるだろう。  

## WebSocket以前の双方向通信
WebSocket以前にも擬似的にサーバーから能動的にクライアントへ通知等を送る技術は存在した。  

### ポーリング
最も安直な実装方法はこれである。  
クライアントのJavaScriptで定期的にサーバーにAjax通信を行うことで、擬似的にサーバーからクライアントに通知を送ることができる。

この方法の利点としては、実装が極めてシンプルであることが挙げれる。
欠点としては、ポーリング間隔が長いとサーバーからの通知の間隔が長くなりリアルタイム性が損なわれるが、ポーリング間隔を短くするとリクエスト数が増えてサーバーの負荷が大きくなるということが挙げれる。

### ロングポーリング(Comet)
ポーリングの応用で、クライアントからのリクエストに対してすぐにレスポンスを返さずに、サーバー側で通知を送りたいときまで待ってからレスポンスを返すという方法がある。

### Server-sent Events
ロングポーリングの応用で、クライアントからのリクエストに対して`text/event-stream`でレスポンスを返し、必要に応じてクライアントにchunkを送る。

## WebSocket
WebSocketはhttpとは異なるプロトコルだが、コネクションの確立までのハンドシェイクにはhttpと同じ形式の通信を使う。
まずクライアントはサーバーに次のようなヘッダを含んだhttpのGETリクエストを送る。

```
GET /chat HTTP/1.1
Host: example.com:8000
Upgrade: websocket
Connection: Upgrade
Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==
Sec-WebSocket-Version: 13
```

これに対してサーバーは次のようなレスポンスを返し、コネクションが確立する
```
HTTP/1.1 101 Switching Protocols
Upgrade: websocket
Connection: Upgrade
Sec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo=
```

`Sec-WebSocket-Accept`はクライアントが送信した`Sec-WebSocket-Key`と`258EAFA5-E914-47DA-95CA-C5AB0DC85B11`を連結した値のSHA1ハッシュをとり、
それをbase64でエンコードした値が入る。  

### サンプル
WebSocketでコネクションを貼るコード。
```csharp
#!/usr/bin/env dotnet-script

using System;
using System.Net;
using System.Net.Sockets;
using System.Security.Cryptography;
using System.Text;
using System.Text.RegularExpressions;

const string WebSocketServerKey = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11";
const int PORT = 8081;
var server = new TcpListener(IPAddress.Parse("127.0.0.1"), PORT);
server.Start();

Print($"Server has started on 127.0.0.1:{PORT}.");

while (true) {
  var client = server.AcceptTcpClient();
  Print("client connected.");
  while (client.Available < 3);

  var stream = client.GetStream();
  while (!stream.DataAvailable);
  var bytes = new Byte[client.Available];

  stream.Read(bytes, 0, bytes.Length);
  var data = Encoding.UTF8.GetString(bytes);

  if (new Regex("^GET").IsMatch(data)) {
    var secWebsocketKey = new Regex("Sec-WebSocket-Key: (.*)").Match(data).Groups[1].Value.Trim();
    var secWebsocketAccept = Convert.ToBase64String(SHA1.Create().ComputeHash(Encoding.UTF8.GetBytes(secWebsocketKey + WebSocketServerKey)));

    var res = Encoding.UTF8.GetBytes(
      "HTTP/1.1 101 Switching Protocols\r\n" +
      "Upgrade: websocket\r\n" +
      "Connection: Upgrade\r\n" +
      "Sec-WebSocket-Accept: " + secWebsocketAccept + "\r\n" +
      "\r\n"
    );

    stream.Write(res, 0, res.Length);
  }
}
```

クライアント側
```html
<html lang="ja">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta http-equiv="X-UA-Compatible" content="ie=edge">
    <title>Document</title>
</head>
<body>
    <input type="text" id="msg">
    <input type="button" id="send_btn" value="Send">
    <div id="log"></div>

    <script>
        const sock = new WebSocket('ws://127.0.0.1:8081');
        const log = document.getElementById("log")

        sock.addEventListener('open', e => {
          log.innerText += "Socket Opend.\n"
        });

        sock.addEventListener("close", e => {
          log.innerText += "Socket Closed.\n"
        })

        sock.addEventListener('message', e => {
          log.innerText += `${e.data}\n`
        });

        document.getElementById("send_btn").addEventListener("click", e => {
          const msg = document.getElementById("msg").value
          sock.send(msg)
        })
    </script>
</body>
</html>
```

### サンプル(チャットアプリ)
Fleckというライブラリを使って簡単なチャットアプリを作ってみた。

```csharp
#r "nuget: Fleck, 1.2.0"
using System.Collections.Generic;
using Fleck;

var server = new WebSocketServer("ws://0.0.0.0:8081");
var connectedSockets = new Dictionary<Guid, IWebSocketConnection>();

server.Start(socket =>
{
  socket.OnOpen = () => {
    connectedSockets.Add(socket.ConnectionInfo.Id, socket);
    Console.WriteLine($"Socket Opened: {socket.ConnectionInfo.Id}");
  };
  socket.OnClose = () => {
    connectedSockets.Remove(socket.ConnectionInfo.Id);
    Console.WriteLine($"Socket Closed: {socket.ConnectionInfo.Id}");
  };
  socket.OnMessage = message => {
    Console.WriteLine(message);
    foreach (var socket in connectedSockets.Values) {
      socket.Send(message);
    }
  };
});

Console.ReadLine();
```
