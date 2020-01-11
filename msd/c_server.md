# C言語でつくるサーバーとC10K問題

## はじめに


なお、今回紹介するサンプルコードはエラー処理が無かったりバッファオーバーフローし放題だったりで全体的にガバガバなので、  
決して外部に公開されているような環境で動かさないこと。  

## 下準備

### ファイルディスクリプタ
サーバーを作る前に、C言語での(というか、POSIXでの)IOについて説明する。  
POSIXでは、ファイル/ネットワーク/デバイス/ターミナル等のIOを抽象化して全てファイルとして扱うようになっている。  
プログラムからするとファイルへデータを読み書きしているつもりであればよく、ファイルの実態が実際のファイルなのか、  
ネットワークソケットなのかターミナルなのか等はプログラムからは基本的に気にする必要が無い。  

プロセルがI/Oを行う場合、
`open`システムコールでファイル(実際のファイルでなくても良い)を開く  
↓  
開いたファイルに`read`/`write`システムコールを実行し、データの読み書きを行う  
↓  
ファイルを使い終わったら`close`システムコールでファイルを閉じる  
という流れになる。  

カレントディレクトリに`tmp.dat`というファイルを作成し、そのファイルに`Hello World!`と書き込むプログラム
```c
#include<sys/types.h>
#include<sys/stat.h>
#include<fcntl.h>
#include<unistd.h>

int main() {
   int fd = open("./tmp.dat", O_CREAT | O_RDWR);
   if (fd < 0) { // ファイルを開くのに失敗した場合
      fprintf(stderr, "Failed to open file.");
      return 1;
   }

   write(fd, "Hello World!\n", 13);
   close(fd);
   return 0;
}
```

`open`システムコールコールの戻り値として、`int`型の値`fd`が返ってきているが、  
これはファイルディスクリプタ(ファイル記述子)と呼ばれる値で、プロセスやカーネルはこの値を元にファイルを識別する。  

ファイルディスクリプタの確認
```c
#include<stdio.h>
#include<unistd.h>
#include<fcntl.h>
#include<sys/stat.h>
#include<sys/types.h>

int main() {
    int fd = open("./tmp2.dat", O_CREAT | O_RDWR);
    printf("fd: %d\n", fd);
    fflush(stdout);

    char buf[256] = {0}; // 0梅
    read(0, buf, 256);
    write(fd, buf, 256);
    close(fd);
    return 0;
}
```
上のプログラムを`fd_test`という名前でコンパイルする。  
コンパイルしたプログラムを実行すると`open`で開いたファイルのファイルディスクリプタ(おそらく3)が表示される。

この状態で他のターミナルから `lsof -d 3` コマンドを実行すると、下のような表示がされる。  
```
$ lsof -d 3
COMMAND    PID   USER   FD      TYPE DEVICE    SIZE              NODE NAME
wslbridge  512 masuda    3u     sock    0,0                      1145 can't identify protocol
node      1264 masuda    3u  unknown                                  anon_inode (stat: Operation not permitted)
node      1306 masuda    3u     sock    0,0                      3459 can't identify protocol
node      1386 masuda    3u     sock    0,0                      3517 can't identify protocol
Microsoft 1491 masuda    3u      REG    0,2 5816320 84442493013196862 /home/masuda/.vscode-server/data/User/workspaceStorage/8541928a180e7f115ef1d8d279ef0fef/ms-vscode.cpptools/.browse.VC.db
Microsoft 2022 masuda    3r     FIFO    0,2          3659174698382459 /tmp/pipe_client_request_1491_9
Microsoft 2051 masuda    3r     FIFO    0,2          2251799814940395 /tmp/pipe_client_request_1491_10
node      2157 masuda    3u     sock    0,0                      5999 can't identify protocol
Microsoft 2623 masuda    3r     FIFO    0,2          7881299349122615 /tmp/pipe_client_request_1491_13
fd_test   2842 masuda    3u      REG    0,2     256 11258999069499900 /home/masuda/dev/cserv/tmp2.dat
lsof      2843 masuda    3r      DIR    0,5       0                 1 /proc
```

下から2番目に `fd_test` と表示されており、3番のファイルディスクリプタを使用していることが分かる。  
上の表示から分かるようにファイルディスクリプタはプロセス毎に一意であるが、システム毎に一意であるわけではない。  
例えばあるプロセスが開いたファイルのファイルディスクリプタが3だった場合、そのプロセスが他のファイルを開いたときに   
他のファイルのファイルディスクリプタが3になることは無い(元のファイルをcloseしない限り)が、  
別のプロセスがファイルを開いたらそのファイルディスクリプタは3になりうる。  
OS側はプロセスIDとファイルディスクリプタの組み合わせでファイルを管理している。  

上の例でファイルディスクリプタが何故いきなり3から始まっているんだという感じだが、
0, 1, 2 の3つのファイルディスクリプタはプロセスの起動時に標準入力, 標準出力, 標準エラー出力として割り当てられているのでそうなっている。  
(というよりも、プロセス起動時に割り当てられる0, 1, 2 の3つのファイルディスクリプタのことを  
標準入力, 標準出力, 標準エラー出力と呼ぶと言った方が多分正しい)  

writeシステムコールを使ったHello World
```c
#include<unistd.h>

int main(void) {
   write(1, "Hello World!\n", 13); // 標準出力へ出力
   return 0;
}
```

readで標準入力を読み込み、それをwriteでそのまま出力する例
```c
#include<unistd.h>

int main() {
    char buf[256] = {0}; // 0埋め
    read(0, buf, 256);　 // 標準入力から読み込み
    write(1, buf, 256);
    return 0;
}
```

### ソケット
UNIXでは(BSD)ソケットという仕組みを使って、プロセス間やネットワークの通信を行う。  


ソケットの利用の流れは次のようになる。  
ソケットを作成  
↓  
作成したソケットをソケットファイルにbind  
↓  
listenでソケットを接続待ちソケットとして登録  
↓  
acceptでソケットへの接続を待ち受ける(ここでブロック)  
↓  
クライアントからの接続があったら、read/writeでデータを送受信  
↓  
ソケットをclose  

UNIXドメインソケットを使ったプロセス間通信  
サーバー
```c
#include<stdio.h>
#include<stdlib.h>
#include<unistd.h>
#include<sys/types.h>
#include<sys/socket.h>
#include<sys/un.h>

int main() {
    int rsock_fd = socket(AF_UNIX, SOCK_STREAM, 0); // ソケットの作成
    if (rsock_fd < 0) {
        fprintf(stderr, "Error. Cannot make socket\n");
        return -1;
    }

    const char * PATH = "/tmp/unix_dsocket_sample_0002"; // ソケットファイルを作成するPATH
    struct sockaddr_un addr;
    addr.sun_family = AF_UNIX;
    strcpy(addr.sun_path, PATH);

    int ret;
    ret = bind(rsock_fd, (struct socketaddr *)&addr, sizeof(addr)); // ソケットをソケットファイルと bind
    if (ret < 0) {
        fprintf(stderr, "Error. Cannot bind socket\n");
        return -1;
    }

    ret = listen(rsock_fd, 5); // 接続待ちソケットとして登録 
    if (ret < 0) {
        fprintf(stderr, "Error. Cannot bind socket\n");
        return -1;
    }

    struct sockaddr_un client;
    int len = sizeof(client);
    int wsock_fd;

    char buf[256];
    
    wsock_fd = accept(rsock_fd, (struct sockaddr *)&client, &len); // クライアントからデータが送信されるまで待機
    if (wsock_fd < 0) {
        fprintf(stderr, "Error.\n");
        return -1;
    }

    ret = read(wsock_fd, buf, 256); // データを読み込んで buf に書き出し
    if (ret < 0) {
        fprintf(stderr, "Error. Cannot bind socket\n");
        return -1;
    }

    printf("%s", buf) 

    // 後始末
    shutdown(wsock_fd, 2);
    close(wsock_fd);    
    shutdown(rsock_fd, 2);
    close(rsock_fd);
    unlink(PATH);

    return 0;
}
```

クライアント
```c
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/un.h>

int main() {
    int wsock_fd = socket(AF_UNIX, SOCK_STREAM, 0);　// ソケットの作成
    if (wsock_fd < 0) {
        fprintf(stderr, "Error. Cannot make socket\n");
        return -1;
    }

    const char * PATH = "/tmp/unix_dsocket_sample_0002";

    struct sockaddr_un addr;
    addr.sun_family = AF_UNIX;
    strcpy(addr.sun_path, PATH);

    int ret;
    ret = connect(wsock_fd, (struct sockaddr *)&addr, sizeof(addr)); // ソケットをソケットファイルと connect
    if (ret < 0) {
        fprintf(stderr, "Error. Cannot connect socket\n");
        return -1;
    }

    char buf[256] = {0};
    strcpy(buf, "From Client\n");

    ret = write(wsock_fd, buf, 256); // ソケット経由でサーバーにデータ送信
    if (ret < 0) {
        fprintf(stderr, "Error. Cannot write.\n");
        return -1;
    }

    // 後始末
    shutdown(wsock_fd, 2);
    close(wsock_fd);

    return 0;
}
```

## その1: シンプルなWebサーバー
ソケットを使って簡単なWebサーバーを作ってみよう。  
とは言ってもソケットの種類がUnixドメインソケットからTCPソケットになるだけで、プログラムは殆ど同じである。  

```c
#include<stdio.h>
#include<unistd.h>
#include<sys/types.h>
#include<sys/socket.h>
#include<netinet/in.h>

int main(void) {
   int rsock = socket(AF_INET, SOCK_STREAM, 0);
   if (rsock < 0) {
      fprintf(stderr, "Error. Cannot make socket\n");
      return -1;
   }

   struct sockaddr_in addr, client;
   addr.sin_family = AF_INET;
   addr.sin_port = htons(8080);
   addr.sin_addr.s_addr = INADDR_ANY;

   int ret = bind(rsock, (struct sockaddr *)&addr, sizeof(addr));
   if (ret < 0) {
      fprintf(stderr, "Error. Cannot bind socket\n");
      return -1;
   }

   listen(rsock, 5);

   int len = sizeof(client);
   int wsock;

   while (1) {
      wsock = accept(rsock, (struct sockaddr *)&client, &len); // ここで block
      if (wsock < 0) {
         fprintf(stderr, "Error. Cannot bind socket\n");
         return -1;
      }
      char buf[2048] = {0};
      if (!read(wsock, buf, 2048))  {
         fprintf(stderr, "Error. Cannot read\n");
         close(wsock);
         close(rsock);
         return -1;
      }

      printf("%s", buf); // クライアントからのHttpリクエストの内容をコンソールに出力

      write(wsock, "HTTP/1.1 200 OK\n", 16);
      write(wsock, "Content-Type: text/plain; charset=UTF-8\n\n", 41);
      write(wsock, "Hello World!!!!", 15);

      close(wsock);
   }
   
   close(rsock);

   return 0;
}
```

## その2: 複数同時リクエストに対応したWebサーバー
上の例の非常に簡単なWebサーバーではプロセスが1つなので同時に1つのクライアントからのリクエストしか処理できないという大きな問題がある。  
そこで、サーバーをマルチプロセス化して複数のリクエストを同時に処理できるようにしてみよう。  

### プロセスとfork
マルチプロセスのサーバーを作る前に、UNIXでのマルチプロセスプログラミングについて説明する。  
UNIXでは`fork`を実行するとプロセスを複製することができる。  

```c
#include<stdio.h>
#include<stdlib.h>
#include<unistd.h>
#include<sys/types.h>
#include<sys/wait.h>

int main() {
    pid_t child_pid = fork();

    if (child_pid < 0) {
        fprintf(stderr, "Failed to fork.");
        return 1;
    }

    if (child_pid == 0) {
        // 子プロセスの処理
        printf("Child Process.\n");
        sleep(3);
        exit(42);
    } else {
        // 親プロセスの処理
        printf("Parent Process.\n");

        int status;
        waitpid(child_pid, &status, 0); // 子プロセスが終了するまで待つ
        
        printf("Child process (PID=%d) exited with status %d.\n", child_pid, WEXITSTATUS(status));
    }

    return 0;
}
```

### fork を利用したWebサーバー
`fork`を利用して、リクエストを受けたらプロセスを複製して子プロセスでリクエストを返すようにしよう。  

```c
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<unistd.h>
#include<sys/types.h>
#include<sys/socket.h>
#include<netinet/in.h>

int main(void) {
    int rsock = socket(AF_INET, SOCK_STREAM, 0);
    if (rsock < 0) {
        fprintf(stderr, "Error. Cannot make socket\n");
        return -1;
    }

    struct sockaddr_in addr, client;
    addr.sin_family = AF_INET;
    addr.sin_port = htons(8080);
    addr.sin_addr.s_addr = INADDR_ANY;

    int ret = bind(rsock, (struct sockaddr *)&addr, sizeof(addr));
    if (ret < 0) {
        fprintf(stderr, "Error. Cannot bind socket\n");
        return -1;
    }

    listen(rsock, 5);

    int len = sizeof(client);
    int wsock;

    while (1) {
        wsock = accept(rsock, (struct sockaddr *)&client, &len); // ここで block
        if (wsock < 0) {
            fprintf(stderr, "Error. Cannot bind socket\n");
            return -1;
        }

        pid_t child_pid = fork(); // 親プロセスでは子プロセスのpidが、子プロセスでは0が返ってくる
 
        if (child_pid < 0) {
            fprintf(stderr, "Error. Failed to fork");
            close(wsock);
            break;
        }

        if (child_pid == 0) { // 子プロセスの処理
            char buf[2048] = {0};

            if (!read(wsock, buf, 2048))  {
                fprintf(stderr, "Error. Cannot read\n");
                close(wsock);
                close(rsock);
                exit(-1);
            }

            printf("%s", buf);

            write(wsock, "HTTP/1.1 200 OK\n", 16);
            write(wsock, "Content-Type: text/plain; charset=UTF-8\n\n", 41);
            write(wsock, "Hello World!!!!", 15);

            close(wsock);
            exit(0);
        }
        else { // 親プロセスの処理
            // 親プロセスでもsocketをcloseしておく
            // (これをしないと通信が終了しない)
            close(wsock); 
        }
    }
    
    close(rsock);

    return 0;
}
```
このプログラムを実行すると一応動くのだが、別のコンソール

ゾンビプロセス(defunctと表示されているのがそれ)
```
$ ps -a
  PID TTY          TIME CMD
    8 tty1     00:00:00 sh
    9 tty1     00:00:00 sh
   14 tty1     00:00:00 sh
   16 tty1     00:00:02 node
   42 tty1     00:00:00 node
  138 tty1     00:00:13 node
  181 tty1     00:00:04 Microsoft.VSCod
  510 tty2     00:00:00 sh
  512 tty2     00:00:00 wslbridge2-back
  625 tty1     00:00:00 Microsoft.VSCod
  682 pts/0    00:00:00 forked_serv
  683 pts/0    00:00:00 forked_serv <defunct>
  684 pts/0    00:00:00 forked_serv <defunct>
  685 pts/0    00:00:00 forked_serv <defunct>
  686 pts/0    00:00:00 forked_serv <defunct>
  687 pts/0    00:00:00 forked_serv <defunct>
  688 pts/0    00:00:00 forked_serv <defunct>
  689 pts/0    00:00:00 forked_serv <defunct>
  690 pts/0    00:00:00 forked_serv <defunct>
  691 pts/0    00:00:00 forked_serv <defunct>
  692 pts/0    00:00:00 forked_serv <defunct>
  693 pts/1    00:00:00 ps
```

最初の`fork`を使ったサンプルでは親プロセスで`waitpid`を呼び出して子プロセスの終了を待っていたが、  
実は親プロセス側で`wait`しないと子プロセスは終了してもずっと残り続けるのである。  

そこで、子プロセスが終了したらそのシグナルを受け取って親プロセスで`waitpid`を実行するようにしよう。  

```c
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<unistd.h>
#include<signal.h>
#include<sys/types.h>
#include<sys/socket.h>
#include<sys/wait.h>
#include<netinet/in.h>

void catch_SIGCHLD(int signo) {
    pid_t child_pid = 0;

    do {
        int child_ret;
        child_pid = waitpid(-1, &child_ret, WNOHANG);
    } while(child_pid>0);
}

int main(void) {
    // 子プロセスがexitした時のシグナルハンドラの設定
    struct sigaction act;
    memset(&act, 0, sizeof(act));
    act.sa_handler = catch_SIGCHLD; 
    sigemptyset(&act.sa_mask);
    act.sa_flags = SA_NOCLDSTOP | SA_RESTART;
    sigaction(SIGCHLD, &act, NULL);

    int rsock = socket(AF_INET, SOCK_STREAM, 0);
    if (rsock < 0) {
        fprintf(stderr, "Error. Cannot make socket\n");
        return -1;
    }

    struct sockaddr_in addr, client;
    addr.sin_family = AF_INET;
    addr.sin_port = htons(8080);
    addr.sin_addr.s_addr = INADDR_ANY;

    int ret = bind(rsock, (struct sockaddr *)&addr, sizeof(addr));
    if (ret < 0) {
        fprintf(stderr, "Error. Cannot bind socket\n");
        return -1;
    }

    listen(rsock, 5);

    int len = sizeof(client);
    int wsock;

    while (1) {
        wsock = accept(rsock, (struct sockaddr *)&client, &len); // ここで block
        if (wsock < 0) {
            fprintf(stderr, "Error. Cannot bind socket\n");
            return -1;
        }

        pid_t child_pid = fork(); // 親プロセスでは子プロセスのpidが、子プロセスでは0が返ってくる
 
        if (child_pid < 0) {
            fprintf(stderr, "Error. Failed to fork");
            close(wsock);
            break;
        }

        if (child_pid == 0) { // 子プロセスの処理
            char buf[2048] = {0};

            if (!read(wsock, buf, 2048))  {
                fprintf(stderr, "Error. Cannot read\n");
                close(wsock);
                close(rsock);
                exit(-1);
            }

            printf("%s", buf);

            write(wsock, "HTTP/1.1 200 OK\n", 16);
            write(wsock, "Content-Type: text/plain; charset=UTF-8\n\n", 41);
            write(wsock, "Hello World!!!!", 15);

            exit(0);
        }
        else { // 親プロセスの処理
            close(wsock);
        }
    }
    
    close(rsock);

    return 0;
}
```

このサンプルではリクエストが来てからプロセスをforkしているが、プロセスをforkすること自体がそこそこ重い処理なので  
実際のWebサーバーでは起動直後にforkして予めリクエストを受け付けるプロセスを複数本用意しておくことが多い(preforkモデル)。  
あるいはプロセスの代わりにより軽量な実行単位であるスレッドを使ったりすることもある(というか、多分そっちの方が主流)。  

## その3: ノンブロッキングIOを利用したWebサーバー
上の実装で問題は解決したかにみえた…  
が、このように1リクエストに対して1プロセス(or 1スレッド)を割り当てるという実行モデルは  
クライアントの数が増えたときに問題になる。  
プロセスというのは起動時に数MByte程度のスタックメモリが割り当てられる。  
仮に10万クライアントからのリクエストを同時に処理するため10万プロセスを起動する場合を考えると、  
1プロセスあたりのスタックメモリの割当が4MByteだとすると、4MByte x 10000 = 40 GByte ものメモリが必要となる。  
また、CPUのコア数を超える数のプロセスを実行する場合、実行するプロセスを細かい時間で切り替えながら実行することになるが、  
この実行プロセスの切り替えという処理も大きなボトルネックになる。  

このような多数のクライアントからの大量の同時リクエストによりサーバーがパンクする問題のことを C10K問題といい、
2009年頃によく取り上げられられた。  

んでこのC10K問題の解決策として、イベント駆動型の

### ノンブロッキングIO
普通のIO系のシステムコールは操作が完了するまでプロセスをブロックする。  
例えば、`accept`はクライアントからのソケットの接続があるまで、`open`はファイルの読み書きの準備ができるまで、  
標準入力に対する`read`はコンソールからの入力が終了するまでプロセスの実行が停止する  
(カーネルのプロセススケジューラーがプロセスをスリープ状態にしておく)  
(`write`はバッファリングがあるので即座にブロックするとは限らない)。  

このことを確かめてみよう。  
最初の例で挙げた`read`/`write`システムコールを使って入力をそのまま出力するプログラムを用意する。  
```c
#include<unistd.h>

int main() {
    char buf[256] = {0}; // 0埋め
    read(0, buf, 256);　 // 標準入力から読み込み
    write(1, buf, 256);
    return 0;
}
```
上のプログラムを `stdin_read` 等適当な名前でコンパイルする。  
コンパイルしたプログラムを実行し、入力待ちの状態になったら別のコンソールから `ps -x`コマンドを実行してみよう。  

```
$ ps -x
  PID TTY      STAT   TIME COMMAND
    8 tty1     S      0:00 sh -c "$VSCODE_WSL_EXT_LOCATION/scripts/wslServer.sh" f359dd69833dd8800b54d458f6d37ab7c78df520 stable .vscode-server 0
  ...
16659 pts/0    S      0:00 ./stdin_read
16674 pts/2    R      0:00 ps -x
```
`stdin_read` のSTATが`S` になっている。  
これは、対象のプロセスが割り込み可能なスリープ状態にあることを表している。  

`man ps` から一部抜粋
```
PROCESS STATE CODES
   Here are the different values that the s, stat and state output specifiers (header "STAT" or "S") will display to describe the state of a process:

      D    uninterruptible sleep (usually IO)
      R    running or runnable (on run queue)
      S    interruptible sleep (waiting for an event to complete)
      T    stopped by job control signal
      t    stopped by debugger during the tracing
      W    paging (not valid since the 2.6.xx kernel)
      X    dead (should never be seen)
      Z    defunct ("zombie") process, terminated but not reaped by its parent
```

このように、IOがプログラムをブロックしてしまうとせっかくCPUに余裕があっても。
この問題の解決策の１つは上に挙げたマルチプロセス化であるが、もう１つの解決策としてノンブロッキングIOを利用するというものがある。  

ノンブロッキングIOとは、その名の通りプロセスをブロッキングしないIO系システムコールである。  
上で述べたように、`open`は普通ファイルの読み書きの準備ができるまで処理をブロックするが、  
オプションで `O_NONBLOCK` を指定すると処理をブロックせずにそのまま制御が戻るようになる。  
こうすると、カーネルは裏でファイルの読み書きの準備をしつつユーザープロセスは別の仕事をするということができる。  
ユーザープロセスがノンブロッキングモードで`open`したファイルに対して`read`/`write`を行うと、  
ファイルの読み書きの準備ができている場合は成功し、まだ準備ができていない場合はおもむろに失敗するということになる。  

ノンブロッキングIOでのファイルの読み込み。  
```c
#include<stdio.h>
#include<unistd.h>
#include<fcntl.h>
#include<sys/stat.h>
#include<sys/types.h>
#include<errno.h>

int main() {
    int fd = open("./tmp2.dat", O_RDONLY | O_NONBLOCK);

    char buf[256];
    int ret;

    while (1) { // readの準備ができるまでポーリング
        ret = read(fd, buf, 256);
        if (ret < 0 && errno == EAGAIN) { // 準備ができていない
            printf("waiting for read.\n");
            continue;
        }
        else if (ret < 0) { // 謎のエラー
            fprintf(stderr, "Failed to write.\n");
            return 1;
        }
        else { // readが成功したのでbreak
            break;
        }
    }

    printf("%s", buf);
        
    ret = close(fd);
    if (ret < 0) {
        fprintf(stderr, "Failed to close.\n");
        return 1;
    }
    return 0;
}
```
上のプログラムを実行するとreadの準備が完了するまで`waiting for read.`と出力された後にファイルの中身が出力される…  
という動作になって欲しいのだが実際は１度も`waiting for read.` と出力されずにファイルの中身が出力される。  

別の例として、標準入力をノンブロッキング化してみよう。  
標準入力は普通はそのままではブロッキングするが、`fcntl`システムコールを使うとオープン済みの  
ファイルディスクリプタを操作してIOをノンブロッキング化することができる。  

標準入力をノンブロッキング化
```c
#include<stdio.h>
#include<unistd.h>
#include<fcntl.h>
#include<sys/stat.h>
#include<sys/types.h>
#include<errno.h>

int main() {
    int flag = fcntl(0, F_GETFD, 0); // 第一引数に指定したFDの状態を表すフラグを取得する
    fcntl(0, F_SETFL, flag | O_NONBLOCK); //第一引数に指定したFDに対してNONBLOCKを設定する

    char buf[256];
    int ret;
    while (1) {
        ret = read(0, buf, 256);
        if (ret < 0 && errno == EAGAIN) {
            printf("waitin for read.\n");
            continue;
        }
        else if (ret < 0) {
            fprintf(stderr, "Failed to read.\n");
            return 1;
        }
        else {
            break;
        }
    }

    printf("input: %s", buf);

    return 0;
}
```

このプログラムを実行すると、標準入力がされるまで`waiting for read.`と出力し、
入力があるとそれを出力して停止する。  

### IO多重化
上の例だと`open`をノンブロッキング化したところで`read`の準備ができるまで結局ポーリングしているのでまるで意味がない。  
POSIXではノンブロッキングIOを有効利用するために、`select`というシステムコールがあり、これを使うと複数のファイルディスクリプタを監視して、  
いずれかのファイルディスクリプタの仕様準備ができたら処理を行うということができる(IOの多重化)。  

```c
#include<sys/time.h>
#include<stdio.h>
#include<unistd.h>
#include<fcntl.h>
#include<sys/stat.h>
#include<sys/types.h>
#include<errno.h>
#include<math.h>

#define max(a, b) ((a > b) ? (a) : (b))

int main(void) {
    int fd1 = open("./tmp1.dat", O_RDWR | O_NONBLOCK);
    int fd2 = open("./tmp2.dat", O_RDWR | O_NONBLOCK);
    
    fd_set rfds; // ファイルディスクリプタの集合
    struct timeval tv;
    /* 5 秒間監視する。*/
    tv.tv_sec = 3;
    tv.tv_usec = 0;

    FD_ZERO(&rfds); // ファイルディスクリプタ集合の初期化
    FD_SET(fd1, &rfds); // ファイルディスクリプタ集合に fd1 を登録
    FD_SET(fd2, &rfds); // ファイルディスクリプタ集合に fd2 を登録

    int ret;
    ret = select(max(fd1, fd2) + 1, &rfds, NULL, NULL, &tv); // ファイルディスクリプタ集合の状態変化を監視
    // この時点(select実行後)での tv の値は変更されるおそれあり

    if (ret < 0) { // 戻り値が 0 より小さいときはエラー
        fpintf(stderr, "select");
    }
    else if (ret == 0) { // 戻り値が 0 のときはタイムアウト
        printf("timeout.\n");
    }
    else { // それ以外のときは ファイルディスクリプタ集合に含まれるファイルディスクリプタの数が返ってくる
        if (FD_ISSET(fd1, &rfds)) {  // 実際にどのファイルディスクリプタが使用可能になったかは FD_ISSET で確かめる
            char buf[2048];
            read(fd1, buf, 2048);
            printf("%s", buf);
        }
        if (FD_ISSET(fd2, &rfds)){
            char buf[2048];
            read(fd2, buf, 2048);
            printf("%s", buf);
        }
    }

    return 0;
}
```

```c
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <netinet/in.h>
#include <unistd.h>
#include <netdb.h>
#include <errno.h>

const int MAX_SOCK = 10;

void die(const char* msg) {
    fprintf(stderr, "%s", msg);
    exit(1);
}

int main() {
    int clie_sock_fds[MAX_SOCK];
    for (int i = 0; i < MAX_SOCK; i++) {
        clie_sock_fds[i] = -1; // 未使用状態は -1 で初期化しておく
    }

    struct servent *serv;

    socklen_t len = sizeof(struct sockaddr_in);
    struct sockaddr_in from_addr;

    char buf[2048] = {0};

    int serv_sock_fd = socket(AF_INET, SOCK_STREAM, 0);
    if (serv_sock_fd < 0) die("Serv socket.");

    struct sockaddr_in addr;
    addr.sin_family = AF_INET;
    addr.sin_port = ntohs(8080);
    addr.sin_addr.s_addr = INADDR_ANY;

    int ret;
    ret = bind(serv_sock_fd, (struct sockaddr *)&addr, sizeof addr);
    if (ret < 0) die("bind.");

    ret = listen(serv_sock_fd, 5);
    if (ret < 0) die("listen.");

    int maxfd;
    fd_set rfds;

    int cnt = 0;
    while (1) {
        FD_ZERO(&rfds);
        FD_SET(serv_sock_fd, &rfds);
        maxfd = serv_sock_fd;
        for (int i = 0; i < MAX_SOCK; i++) {
            if (clie_sock_fds[i] != -1) {
                FD_SET(clie_sock_fds[i], &rfds);
                if (clie_sock_fds[i] > maxfd) {
                    maxfd = clie_sock_fds[i];
                }
            }
        }
        
        struct timeval tv;
        tv.tv_sec = 30;
        tv.tv_usec = 0;
        
        cnt = select(maxfd + 1, &rfds, NULL, NULL, &tv);

        if (cnt < 0) {
            if (errno == EINTR) continue;
            else die("Unkown error");
        }
        else if (cnt == 0) {
            printf("timeout\n");
        }
        else {
            if (FD_ISSET(serv_sock_fd, &rfds)) {
                for (int i = 0; i < MAX_SOCK; i++) {
                    if (clie_sock_fds[i] == -1) { // 未使用があったらacceptに使う
                        clie_sock_fds[i] = accept(serv_sock_fd, (struct sockaddr *)&from_addr, &len);
                        if (clie_sock_fds[i] < 0) die("accept");
                        printf("socket %d connected.\n", clie_sock_fds[i]);
                        break;
                    }
                }
            }

            for (int i = 0; i < MAX_SOCK; i++) {
                if (FD_ISSET(clie_sock_fds[i], &rfds)) {
                    cnt = read(clie_sock_fds[i], buf, 2048);
                    if (cnt < 0) {
                        break;
                    } else {
                        printf("%s\n", buf);

                        write(clie_sock_fds[i], "HTTP/1.1 200 OK\n", 16);
                        write(clie_sock_fds[i], "Content-Type: text/plain; charset=UTF-8\n\n", 41);
                        write(clie_sock_fds[i], "Hello World!!!!", 15);
                        
                        close(clie_sock_fds[i]);

                        printf("socket %d disconnected.\n", clie_sock_fds[i]);
                        clie_sock_fds[i] = -1; // close したら未使用に戻す
                    }
                }
            }
        }
    }
}
```

## 参考資料
ネットワークサービスは必ずforkしよう[https://www.ipa.go.jp/security/awareness/vendor/programmingv1/b07_04.html]  
[https://www.aihara.co.jp/~junt/program/socket.html]
Linuxネットワークプログラミング(シングルプロセス、シングルスレッドで多重化) [https://www.infra.jp/programming/network_programming_3.html]
